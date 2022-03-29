fun binop_t s t1 t2 = mk_fun s [t1,t2]

fun unop_t s t = mk_fun s [t]

val And = binop_t "And"

val Or = binop_t "Or"

val Imp = binop_t "Imp"

val Iff = binop_t "Iff"

val id = unop_t "id"

val ALL = unop_t "ALL";

val EX = unop_t "EX";

val UE = unop_t "UE";

fun dest_ar s = 
    case view_sort s of
       vSrt("ar",[d,c]) => (d,c) 
     | _ => raise simple_fail "not an arr"

val dom = fst o dest_ar 
val cod = snd o dest_ar 

fun bounds f = 
    case view_form f of 
        vQ(q,n,s,b) => (n,s) :: bounds b
      | vConn(_,[f]) => bounds f
      | vConn(_,[f1,f2]) => (bounds f1) @ (bounds f2)
      | vPred _ => []
      | vConn(_,l) => raise simple_fail "bounds.wrong input"

fun Pol l = 
    case l of 
       [] => raise ERR ("Pol.empty input",[],[],[])
      |h :: t => 
       (case t of 
           [] => h
         | h1 :: t1 => 
           (case t1 of 
               [] => Po h h1
             | h2 :: t2 => 
               Po h (Pol t)))

fun mk_pj n1 n2 =
    mk_fun ("p" ^ (Int.toString n1) ^ (Int.toString n2))

fun mk_pj n1 n2 =
    if n1 = 1 andalso n2 = 1 then mk_fun "id" 
    else if n1 = 2 andalso n2 = 1 then mk_fun "p1" 
    else if n1 = 2 andalso n2 = 2 then mk_fun "p2"
    else
    mk_fun ("p" ^ (Int.toString n1) ^ (Int.toString n2))


fun pos n l = 
    case l of 
        [] => raise simple_fail "pos.not a list member"
      | h :: t => if h = n then 1 else (pos n t) + 1

fun Pal l = 
    case l of 
       [] => raise ERR ("Pal.empty input",[],[],[])
      |h :: t => 
       (case t of 
           [] =>  h
         | h1 :: t1 => 
           (case t1 of 
               [] => Pa h h1
             | h2 :: t2 => 
               Pa h (Pal t)))


(*fsym dict records the information that:
Sub(n1,n2) should be SUB o Pa(n1,n2),
so it does not build IL terms with Sub, but SUB.

and hence not require the rw to expand the def of Sub to get distrib.

only record the string and the term that the function symbol coressponds. Assuming they corresponds as uniform as:
Sub(n1,n2) |-> SUB o Pa2(n1,n2)
Same as Mul, Add, and for unary:

Suc(n) |-> Suc o Pa1(n) (:= Suc o n)

*)
fun inserts d l = List.foldr (fn ((a,b),d) => Binarymap.insert(d,a,b)) d l



val psym2IL0 = inserts (Binarymap.mkDict String.compare)
[("IN",(rastt "In(X)",
        [("x",ar_sort (mk_ob "A") (mk_ob "X")),
         ("xs",ar_sort (mk_ob "A") (rastt "Exp(X,1+1)"))]))]


(*Ins(x0:1->X,s0:1->Exp(X,2)) |-> INS(X) o Pa(x0,s0) *)
val fsym2IL0 = inserts (Binarymap.mkDict String.compare)
[("Ins",(rastt "INS(X)",[("x",ar_sort (mk_ob "A") (mk_ob "X")),
         ("xs",ar_sort (mk_ob "A") (rastt "Exp(X,1+1)"))]))]

val fsym2IL = ref fsym2IL0

(*
fun new_fsym2IL (fsym,fterm) = 
fsym2IL := Binarymap.insert(!fsym2IL,fsym,fterm)
*)

fun new_fsym2IL (fsym,(ft,args)) = 
fsym2IL := Binarymap.insert(!fsym2IL,fsym,(ft,args))


fun new_fsym2IL1 (fsym,fterm) = 
fsym2IL := Binarymap.insert(!fsym2IL,fsym,(fterm,[]))


fun corres_fterm (ft,args) tl = 
    if args = [] then ft else
    let val env = match_tl essps (List.map mk_var args) tl emptyvd
    in inst_term env ft
    end

fun term2IL bvs t =
    let val doms = List.map (cod o snd) bvs
        val tn = length doms
        val vdom = el tn doms
    in
        case view_term t of 
            vVar(n,s) => 
            if not $ mem (n,s) bvs then 
               binop_t "o" t (unop_t "To1" (Pol doms))
            else mk_pj tn (pos (n,s) bvs) doms
          | vFun("o",s,[f,t]) =>
            mk_o f (term2IL bvs t)
          | vFun(f,s,tl) => 
            if length tl = 0 orelse 
               List.exists (fn t => sort_of t = ob_sort) tl 
                           (*due to polymorphic costant*)
            then binop_t "o" t (unop_t "To1" (Pol doms))
            else
                let val args = List.map (term2IL bvs) tl
                in
                case Binarymap.peek(!fsym2IL,f) of 
                    SOME finfo =>  binop_t "o" (corres_fterm finfo tl) (Pal args)
                  | NONE => mk_fun f args
                end
          | _ => raise simple_fail "bound variables should not be here"
    end;  




val truth = mk_fun "TRUE" []


fun mk_pred_ap pt args = (mk_o pt (Pal args))





val psym2IL0 = inserts (Binarymap.mkDict String.compare)
[("IN",(rastt "In(X)",
        [("x",ar_sort (mk_ob "A") (mk_ob "X")),
         ("xs",ar_sort (mk_ob "A") (rastt "Exp(X,1+1)"))]))]
(*
[("Le",(rastt "Char(LE)",[])),
 ("Lt",(rastt "Char(LT)",[])),(*
 ("HasCard",(rastt "hasCard(X)",
             [("xs",ar_sort (mk_ob "A") (rastt "Exp(X,1+1)")),
              ("n",ar_sort (mk_ob "A") N)])),*)
 ("Even",(rastt "EVEN",[])),
 ("IN",(rastt "Mem(X)",
        [("x",ar_sort (mk_ob "A") (mk_ob "X")),
         ("xs",ar_sort (mk_ob "A") (rastt "Exp(X,1+1)"))])),
 ("Sim",(rastt "relJ",[]))]
*)

val psym2IL = ref psym2IL0

fun new_psym2IL (pred,(predfun,inputs)) = 
psym2IL := Binarymap.insert(!psym2IL,pred,(predfun,inputs))

(*
form2IL [dest_var $ rastt "xs:1->Exp(X,1+1)",dest_var $ rastt "n:1->N"]
“!x:1->K.HasCard(xs:1->Exp(X,1+1),n:1->N)” 
keep this example

*)


val DISJ = mk_fun "DISJ" []

val IFF = mk_fun "IFF" []

val NEG = mk_fun "NEG" []

fun binop_t s t1 t2 = mk_fun s [t1,t2]

fun unop_t s t = mk_fun s [t]

fun And p q = mk_o CONJ (Pa p q)

fun Or p q = mk_o DISJ (Pa p q)

fun Imp p q = mk_o IMP (Pa p q)

fun Iff p q = mk_o IFF (Pa p q)

fun Neg p = mk_o NEG p

val id = unop_t "id"
 
fun dest_cross AB = 
    case view_term AB of 
        vFun("*",_,[A,B]) => (A,B)
      | _ => raise simple_fail "dest_cross.not a product"


fun ALL f = 
    let val d = dom (sort_of f)
        val (X,Y) = dest_cross d
    in mk_o (mk_fun "All" [X]) (Tp f)
    end 


fun EX f = 
    let val d = dom (sort_of f)
        val (X,Y) = dest_cross d
    in mk_o (mk_fun "Ex" [X]) (Tp f)
    end 


fun UE f = 
    let val d = dom (sort_of f)
        val (X,Y) = dest_cross d
    in mk_o (mk_fun "UE" [X]) (Tp f)
    end 



fun form2IL bvs f = 
    case view_form f of 
        vConn("&",[f1,f2]) => 
        And (form2IL bvs f1) (form2IL bvs f2)
      | vConn("|",[f1,f2]) => 
        Or (form2IL bvs f1) (form2IL bvs f2)
      | vConn("==>",[f1,f2]) => 
        Imp (form2IL bvs f1) (form2IL bvs f2)
      | vConn("<=>",[f1,f2]) => 
        Iff (form2IL bvs f1) (form2IL bvs f2)
      | vConn("~",[f0]) =>
        Neg (form2IL bvs f0)
      | vPred("=",true,[t1,t2]) =>
        mk_pred_ap (mk_fun "Eq" [cod (sort_of t2)])
         [term2IL bvs t1,term2IL bvs t2]
      | vPred(P,_,tl) => 
        (case Binarymap.peek(!psym2IL,P) of
            SOME (p,l) => 
            if l = []  then
                mk_pred_ap p (List.map (term2IL bvs) tl)
            else let val env = match_tl essps (List.map mk_var l) 
                                        (List.map (term2IL bvs) tl) emptyvd
                     in mk_pred_ap (inst_term env p) (List.map (term2IL bvs) tl)
                 end
          | _ => raise simple_fail ("form2IL.pred: " ^ P ^ " not found"))
      | vQ ("!",n,s,b) => ALL (form2IL ((n,s) :: bvs) b)
      | vQ ("?",n,s,b) => EX (form2IL ((n,s) :: bvs) b)
      | vQ ("?!",n,s,b) => UE (form2IL ((n,s) :: bvs) b)
      | _ => raise ERR ("form2IL.ill-formed formula",[],[],[f])


