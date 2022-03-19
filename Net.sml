structure Net :> Net = 
struct
open term form

datatype tlabel
    = V
    | Fn of string


datatype 'a tnet
    = LEAF of (term * 'a) list
    | NODE of (tlabel * 'a tnet) list;



fun tlabel_of tm =
   if is_var tm then V else
   let val (f,_,_) = dest_fun tm
   in Fn f
   end

val empty = NODE [];

fun is_empty (NODE[]) = true
  | is_empty    _     = false;


fun net_assoc label =
 let fun get (LEAF _) = raise simple_fail "net_assoc.LEAF: no children"
       | get (NODE subnets) =
            case assoc1 label subnets
             of NONE => empty
              | SOME (_,net) => net
 in get
 end

fun overwrite (p as (a,_)) =
  let fun over [] = [p]
        | over ((q as (x,_))::rst) =
            if (a=x) then p::rst else q::over rst
  in over
  end;



local
  fun mtch tm (NODE []) = []
    | mtch tm net =
       let val label = tlabel_of tm
           val Vnet = net_assoc V net
           val nets =
            case label
             of V => []
              | Fn f =>
                let val (_,s,ts) = dest_fun tm
                    val net0 = net_assoc label net
                in itlist mtchs (rev ts) [net0]
                end
       in itlist (fn NODE [] => I | net => cons net) nets [Vnet]
       end
  and mtchs t [] = []
    | mtchs t (nhd :: ntl) = append (mtch t nhd) (mtchs t ntl)
in
fun match tm net =
  if is_empty net then []
  else
    itlist (fn LEAF L => append (List.map #2 L) | _ => fn y => y)
           (mtch tm net) []
end;



fun tinsert (pair as (tm,_)) N =
let fun enter _ _  (LEAF _) = raise simple_fail "insert.LEAF: cannot insert"
   | enter defd tm (NODE subnets) =
      let val label = tlabel_of tm
          val child =
             case assoc1 label subnets of NONE => empty | SOME (_,net) => net
          fun exec [] (LEAF L)  = LEAF(pair::L)
            | exec [] (NODE _)  = LEAF[pair]
            | exec (h::rst) net = enter rst h net
          val new_child =
              case label
               of Fn f =>
                  let val (_,_,ts) = dest_fun tm
                  in if ts = [] then exec defd child
                     else enter ((tl ts) @ defd) (hd ts) child
                  end
              | _ => exec defd child
      in
         NODE (overwrite (label,new_child) subnets)
      end
in enter [] tm N
end;



datatype flabel
    = Q of string
    | Cn of string
    | fV
    | Pr of string
    | tV
    | tFn of string


datatype 'a fnet
    = fLEAF of 'a list
    | fNODE of (flabel,'a fnet) Binarymap.dict;

fun flabel_cpr p =
    case p of
        (Q s1,Q s2) => String.compare (s1,s2)
      | (Q _,_) => LESS
      | (_,Q _) => GREATER
      | (Cn s1,Cn s2) => String.compare (s1,s2)
      | (Cn _,_) => LESS
      | (_,Cn _) => GREATER
      | (Pr s1,Pr s2) => String.compare (s1,s2)
      | (Pr _,_) => LESS
      | (_,Pr _) => GREATER
      | (tFn s1,tFn s2) => String.compare (s1,s2)
      | (tFn _,_) => LESS
      | (_,tFn _) => GREATER
      | (tV,fV) => LESS
      | (fV,tV) => GREATER
      | _ => EQUAL


fun mk_fempty () = fNODE (Binarymap.mkDict flabel_cpr)

val fempty: (fconv fnet) = fLEAF []

fun is_fempty (fNODE nets) = Binarymap.numItems nets = 0
  | is_fempty _ = false



fun flabel_of fm =
    case view_form fm of
        vPred (P,true,_) => Pr P
      | vPred (P,false,_) => fV
      | vConn(co,_) => Cn co
      | vQ(q,_,_,_) => Q q

fun tlabel_of tm =
    case view_term tm of
        vVar _ => tV
     | vFun(f,_,_) => tFn f
     | _ => raise Fail "cannot label bounded var"


fun fnet_assoc label =
 let fun get (fLEAF _) = raise simple_fail "fnet.assoc: LEAF: no children"
       | get (fNODE subnets) =
            case Binarymap.peek(subnets,label)
             of NONE => fempty
              | SOME net => net
 in get
 end

fun dest_quant f =
    case view_form f of
        vQ(_,_,_,b) => b
      | _ => raise ERR ("dest_quant.not a quantified formula",[],[],[f])


fun dest_conn f =
    case view_form f of
        vConn(co,[f1,f2]) => (f1,f2)
      | _ => raise ERR ("dest_conn.not a (binary) connective",[],[],[f])




local
    fun tmtch tm (fLEAF []) = []
      | tmtch tm net =
        let val label = tlabel_of tm
            val Vnet = fnet_assoc tV net
            val nets =
                case label
                 of tV => []
                  | tFn f =>
                    let val (_,s,ts) = dest_fun tm
                        val net0 = fnet_assoc label net
                    in itlist tmtchs (rev ts) [net0]
                    end
                  | _ => raise Fail "should be a term"
        in itlist (fn fLEAF [] => I | net => cons net) nets [Vnet]
        end
  and tmtchs t [] = []
    | tmtchs t (nhd :: ntl) = append (tmtch t nhd) (tmtchs t ntl)
  fun fmtch fm (fLEAF []) = []
    | fmtch fm net =
       let val label = flabel_of fm
           val Vnet = fnet_assoc fV net
           val nets =
            case label
             of fV => let val (_,ts) = dest_fvar fm
                            val net0 = fnet_assoc label net
                        in itlist tmtchs (rev ts) [net0]
                        end
              | Pr _ => let val (_,ts) = dest_pred fm
                            val net0 = fnet_assoc label net
                        in itlist tmtchs (rev ts) [net0]
                        end
              | Q _    => fmtch (dest_quant fm) (fnet_assoc label net)
              | Cn co   =>
                if co = "~" then
                    fmtch (dest_neg fm) (fnet_assoc label net)
                else
                    let val (lf,rf) = dest_conn fm
                          in itlist(append o fmtch rf)
                                   (fmtch lf (fnet_assoc label net)) []
                           end
              | _ => raise Fail "should be a form"
       in itlist (fn fLEAF [] => I | net => cons net) nets [Vnet]
       end
in
fun fmatch fm net =
  if is_fempty net then []
  else
    itlist (fn fLEAF L => append L | _ => fn y => y)
           (fmtch fm net) []
end;



fun dest_any_pred fm =
    case view_form fm of
        vPred (p,_,ts) => (p,ts)
      | _ => raise ERR ("dest_any_pred.not a pred or formula variable",[],[],[fm])



datatype TorF = Tm of term | Fm of form




fun finsert (pair as (fm,c)) N =
let
fun  tenter defd tm (fLEAF []) = tenter defd tm (fNODE (Binarymap.mkDict flabel_cpr))
   | tenter _ _ (fLEAF _) = raise simple_fail "insert.LEAF: cannot insert"
   | tenter defd tm (fNODE subnets) =
      let val label = tlabel_of tm
          val child =
             case Binarymap.peek(subnets,label) of
                 NONE => fempty | SOME net => net
          val new_child =
              case label
               of tFn f =>
                  let val (_,_,ts) = dest_fun tm
                  in if ts = [] then exec defd child
                     else tenter ((List.map Tm (tl ts)) @ defd) (hd ts) child
                  end
              | _ => exec defd child
      in
         fNODE (Binarymap.insert(subnets,label,new_child))
      end
and fenter defd fm  (fLEAF []) = fenter defd fm (fNODE (Binarymap.mkDict flabel_cpr))
   | fenter defd fm (fLEAF _) = raise simple_fail ("finsert.LEAF: cannot insert")
   | fenter defd fm (fNODE subnets) =
      let val label = flabel_of fm
          val child =
             case Binarymap.peek(subnets,label) of NONE => fempty
                                        | SOME net => net
          val new_child =
            case label
             of Cn co =>
                if co = "~" then
                    fenter defd (dest_neg fm) child
                else
                    let val (lf,rf) = dest_conn fm
                    in fenter ((Fm rf)::defd) lf child
                    end
              | Q _ => fenter defd (dest_quant fm) child
              | Pr _ => let val (P,ts) = dest_pred fm
                        in exec ((List.map Tm ts) @ defd) child
                        end
              | fV => let val (P,ts) = dest_fvar fm
                      in exec ((List.map Tm ts) @ defd) child
                      end
              | _ => raise simple_fail "form expected"
      in
         fNODE (Binarymap.insert(subnets,label,new_child))
      end
and exec [] (fLEAF L)  = fLEAF(c::L)
  | exec [] (fNODE nets)  = fLEAF[c]
      | exec (h::rst) net =
        case h of Tm t => tenter rst t net
                | Fm f => fenter rst f net
in fenter [] fm N
end;

datatype 'a fnet0
    = fleaf of 'a list
    | fnode of (flabel * 'a fnet0) list;

fun show_net (fLEAF l) = fleaf l
  | show_net (fNODE dict) =
    let val nets = Binarymap.listItems dict
        val nets0 = List.map (fn (a,b) => (a,show_net b)) nets
    in fnode nets0
    end
end
