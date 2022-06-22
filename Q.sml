structure Q :> Q = 
struct
open drule tactic HOLPP;

fun q2str [QUOTE s] = s

fun qparse_form_with_cont ct fq =
    parse_form_with_cont ct (q2str fq)

fun qparse_term_with_cont ct tq =
    parse_term_with_cont ct (q2str tq)

fun qterm_tac ttac tq: tactic =
    fn (ct,asl,w) => ttac (qparse_term_with_cont ct tq) (ct,asl,w)

fun qterml_tac tltac qtl: tactic = 
    fn (ct,asl,w) => 
       tltac (List.map 
                  (qparse_term_with_cont ct) qtl)
             (ct,asl,w)

fun qform_tac ftac qt: tactic =
    fn (ct,asl,w) =>
       ftac (qparse_form_with_cont ct qt) (ct,asl,w)

val qexists_tac = qterm_tac exists_tac

val qexistsl_tac = qterml_tac existsl_tac

val qabbrev_tac  = qform_tac abbrev_tac

val qsuff_tac = qform_tac suffices_tac

val qby_tac = qform_tac by_tac

val qcases = qform_tac cases_on


fun qterml_tcl (tltcl:term list -> thm_tactic -> thm_tactic) qtl thtac th :tactic = 
    fn (ct,asl,w) => tltcl (List.map (qparse_term_with_cont ct) qtl) thtac th (ct,asl,w)

val qspecl_then = qterml_tcl specl_then


fun qterm_rule (rule:term -> thm -> thm) tql th = rule (qparse_term_with_cont (cont th) tql) th
fun qterml_rule (rule:term list -> thm -> thm) tql th = rule (List.map (qparse_term_with_cont (cont th)) tql) th
val qspec = qterm_rule spec
val qspecl = qterml_rule specl

fun qpick_assum fq (thtac:thm_tactic): tactic = 
    fn (ct,asl,w) => 
       pick_assum (qparse_form_with_cont ct fq) 
                  thtac (ct,asl,w) 

fun qpick_x_assum fq (thtac:thm_tactic): tactic = 
    fn (ct,asl,w) => pick_x_assum (qparse_form_with_cont ct fq)  thtac (ct,asl,w) 

fun qgen qt th = genl [dest_var o qparse_term_with_cont (cont th) $ qt] th


fun simple_genl vsl th = 
    case  vsl of 
        [] => th
      | h :: t => allI h (simple_genl t th) 

fun qgenl qtl th = simple_genl (List.map (dest_var o qparse_term_with_cont (cont th)) qtl) th

val qsspecl_then = qterml_tcl sspecl_then

val qsspecl = qterml_rule sspecl


fun qdefine_fsym (fname,ql) qt = 
    let val tl = List.map (qparse_term_with_cont essps) ql
        val ct0 = fvtl tl
        val t = qparse_term_with_cont ct0 qt
        val vl = List.map dest_var tl
    in define_fsym (fname,vl) t
    end

fun qdefine_psym (pname,ql) qf = 
    let val tl = List.map (qparse_term_with_cont essps) ql
        val ct0 = fvtl tl
        val f = qparse_form_with_cont ct0 qf
        val vl = List.map dest_var tl
    in define_psym (pname,vl) f
    end

(*
fun qSKOLEM fname qvl th = 
    let val tl = List.map (qparse_term_with_cont (cont th)) qvl 
        val vl = List.map dest_var tl
    in SKOLEM1 fname vl th
    end

*)

end
