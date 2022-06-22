structure logic :> logic = 
struct
open term form

datatype thm = thm of ((string * sort) set * form list * form) 
datatype thm_view = vThm of ((string * sort) set * form list * form) 

fun view_thm (thm(G,A,C)) = vThm (G,A,C)

fun dest_thm (thm(G,A,C)) = (G,A,C)

fun mk_thm (G,A,C) = thm(G,A,C)

fun mk_fth f = thm(fvf f,[],f)

fun ant (thm(_,A,_)) = A

fun concl (thm(_,_,C)) = C 

fun cont (thm(G,_,_)) = G

fun eq_thm th1 th2 = 
    HOLset.equal(cont th1,cont th2) andalso
    eq_forml (ant th1) (ant th2) andalso
    eq_form (concl th1, concl th2)

(**********************************************************************

A, Γ |- C
-------------------- inst_thm env
A', Γ' |- C'

A',C' is obtained by pluging in variables recorded in env
Γ' is obtained by collecting all variables in substituted Γ.

**********************************************************************)

(*fun mk_sss l = List.foldr HOLset.union essps l *)

fun inst_thm env th = 
    if is_wfmenv env then
        let
            val G0 = HOLset.listItems (cont th)
            val G = var_bigunion (List.map (fvt o (inst_term (vd_of env)) o mk_var) G0)
            val A = List.map (inst_form env) (ant th)
            val C = inst_form env (concl th)
           (* val _ = HOLset.isSubset(HOLset.union(fvfl A,fvf C),G) orelse raise simple_fail "extra variable caused by inst_thm"*)
            val G1 = HOLset.union(G,fvfl (C :: A))
        in
            thm(G1,A,C)
        end
    else raise simple_fail "bad environment"

fun asml_U (asml:(form list) list) = 
    case asml of 
        [] => []
      | h :: t => op_union (curry eq_form) h (asml_U t)

fun contl_U contl = 
    case contl of 
        [] => HOLset.empty (pair_compare String.compare sort_compare)
      | h :: t => HOLset.union(h,contl_U t)

(*primitive inference rules*)

fun assume f = thm (fvf f,[f],f)

fun conjI (thm (G1,A1,C1)) (thm (G2,A2,C2)) = 
    thm (contl_U [G1,G2],asml_U [A1,A2],mk_conj C1 C2)
   
fun conjE1 (thm(G,A,C)) = 
    let 
        val (C1,_) = dest_conj C
    in 
        thm (G,A,C1)
    end

fun conjE2 (thm(G,A,C)) = 
    let 
        val (_,C2) = dest_conj C
    in 
        thm (G,A,C2)
    end

fun disjI1 f (thm (G,A,C)) = thm (contl_U[G,fvf f],A,mk_disj C f)

fun disjI2 f (thm (G,A,C)) = thm (contl_U[G,fvf f],A,mk_disj f C)

(**********************************************************************

A |- t1 \/ t2 ,   A1,t1 |- t ,   A2,t2|- t
-------------------------------------------------- disjE
A u A1 u A2 |- t

**********************************************************************)

fun disjE th1 th2 th3 = 
    let val (A,B) = dest_disj(concl th1)
        val _ = eq_form(concl th2, concl th3)
                orelse raise ERR ("disjE.conclsions of th#2, th#3 not equal",[],[],[concl th2,concl th3])
        val _ = fmem A (ant th2) orelse
                raise ERR ("disjE.first disjunct not in the formula list: ",
                           [],[],[A])
        val _ = fmem B (ant th3) orelse
                raise ERR ("disjE.second disjunct not in the formula list: ",
                           [],[],[B])
    in
        thm(contl_U [cont th1,cont th2, cont th3],asml_U [ant th1,ril A (ant th2),ril B (ant th3)],
            concl th3)
    end


fun thml_eq_pairs (th:thm,(ll,rl,asml)) = 
    if is_eq (concl th) then  
        let 
            val (l,r) = dest_eq (concl th)
            val asm = ant th
        in 
            (l::ll,r::rl,asml_U [asm,asml])
        end
    else 
        raise ERR ("thml_eq_pairs.input thm is not an equality: ",
                   [],[],[concl th])

fun EQ_fsym f thml = 
    case lookup_fun (!fsyms) f of 
        NONE => raise simple_fail ("EQ_fsym.function: " ^ f ^ " is not found")
      | SOME(s,l) => 
        let 
            val (ll,rl,asml) = List.foldr thml_eq_pairs ([],[],[]) thml
        in
            thm (contl_U (List.map cont thml),asml,
                 mk_eq (mk_fun f ll) (mk_fun f rl))
        end



                
fun EQ_psym p thml = 
    case lookup_pred (!psyms) p of 
        NONE => if p = "=" then 
                    let 
                        val sl = List.map (fst o dest_eq o concl) thml
                        val (ll,rl,asml) = List.foldr thml_eq_pairs ([],[],[]) thml
                        fun mkeq l = case l of [t1,t2] => mk_eq t1 t2
                                             | _ =>  raise ERR ("EQ_psym.mkeq.not a 2-item list",[],l,[])
                    in 
                        thm (contl_U (List.map cont thml),asml,
                             mk_dimp (mkeq ll) (mkeq rl))
                    end
                else raise simple_fail ("EQ_psym.predicate: " ^ p ^ " is not found")
      | SOME l => 
        let 
            val sl = List.map (fst o dest_eq o concl) thml
            val (ll,rl,asml) = List.foldr thml_eq_pairs ([],[],[]) thml
        in 
            thm (contl_U (List.map cont thml),asml,
                 mk_dimp (mk_pred p ll) (mk_pred p rl))
        end



              
fun EQ_psym p thml = 
    if p = "=" then 
        let 
            val sl = List.map (fst o dest_eq o concl) thml
            val (ll,rl,asml) = List.foldr thml_eq_pairs ([],[],[]) thml
            fun mkeq l = case l of [t1,t2] => mk_eq t1 t2
                                 | _ =>  raise ERR ("EQ_psym.mkeq.not a 2-item list",[],l,[])
        in 
            thm (contl_U (List.map cont thml),asml,
                 mk_dimp (mkeq ll) (mkeq rl))
        end
    else 
        let val sl = List.map (fst o dest_eq o concl) thml
            val (ll,rl,asml) = List.foldr thml_eq_pairs ([],[],[]) thml
        in case lookup_pred (!psyms) p of 
               SOME _ => 
               thm (contl_U (List.map cont thml),asml,
                    mk_dimp (mk_pred p ll) (mk_pred p rl))
             | _ => thm (contl_U (List.map cont thml),asml,
                    mk_dimp (mk_fvar p ll) (mk_fvar p rl))
        end





fun tautI f = thm(fvf f,[],mk_disj f (mk_neg f))

(*TODO find all drule that use it and take tautI out!!!!!!!\
 add an axiom instead.
*)

fun negI f (thm (G,A,C)) = 
    let 
        val _ = eq_form(C,FALSE) orelse 
                raise ERR ("negI.concl of thm is not FALSE",
                          [],[],[C])
        val _ = fmem f A orelse
                raise ERR ("negI.formula to be negated not in the asl",
                           [],[],[f])
    in
        thm (G,ril f A, mk_neg f)
    end

fun negE (thm (G1,A1,C1)) (thm (G2,A2,C2)) = 
    let 
        val _ = eq_form(C2,mk_neg C1) orelse 
                raise ERR ("negE.not a pair of contradiction",
                           [],[],[C1,C2])
    in
        thm (contl_U [G1,G2],asml_U [A1,A2],FALSE)
    end

fun falseE fl f = 
    let val _ = fmem FALSE fl orelse 
                raise simple_fail "falseE.FALSE is not in the asl"
    in
        thm(fvfl (f::fl),fl,f)
    end

        
fun trueI A = thm (fvfl A,A,TRUE)

fun dimpI (thm (G1,A1,I1)) (thm (G2,A2,I2)) =
    let 
        val (f1,f2) = dest_imp I1
        val (f3,f4) = dest_imp I2
        val _ = eq_form(f1,f4) andalso eq_form(f2,f3) orelse
                raise ERR ("dimpI.no match",
                           [],[],[I1,I2])
    in
        thm (contl_U[G1,G2],asml_U[A1,A2],mk_dimp f1 f2)
    end

fun dimpE (thm(G,A,C)) = 
    let
        val (f1,f2) = dest_dimp C
    in
        thm(G,A,mk_conj (mk_imp f1 f2) (mk_imp f2 f1))
    end

fun depends_on (n,s) t = HOLset.member(fvt t,(n,s))

fun allI (ns as (a,s)) (thm(G,A,C)) = 
    let 
        val G0 = HOLset.delete(G,ns) 
                 handle _ => G
        val D0 = HOLset.listItems $ HOLset.difference(fvs s,G0) (*HOLset.numItems gives size of set, can merge in the variable into G0 and remove this check*)
        val _ = List.length D0 = 0 orelse
                raise ERR ("sort of the variable to be abstract has extra variable(s)",[],List.map mk_var D0,[])  
        val _ = case HOLset.find
                         (fn (n0,s0) => depends_on ns (mk_var (n0,s0))) G0 of 
                    NONE => ()
                  | SOME _ => 
                    raise simple_fail
                          "variable to be abstract occurs in context" 
        val _ = not (HOLset.member(fvfl A,ns)) orelse 
                raise simple_fail "variable to be abstract occurs in assumption" 
    in thm(G0,A,mk_forall a s C)
    end


(**********************************************************************

A,Γ |- !x:s. ϕ(x),  |=_s t: s
---------------------------------------- allE, requires sort of t is s
A,Γ u (Var(t)) |- ϕ(t)


rastt "Pr(f:X->A,g:X->B)" 

 "*" 

|=_s A:ob  |=_s B:ob
-----
|=_s A * B: ob

a1: S1....an:Sn /\ A1 /\ ... /\ Am ==> !x. x:s ==> phi(x)
------------------------ 
a1: S1....an:Sn /\ A1 /\ ... /\ Am ==> ... & t:s ==> phi(t)

f:A->B f:C->D

ar




**********************************************************************)

fun allE t (thm(G,A,C)) = 
    let 
        val (ns as (n,s),b) = dest_forall C
        val _ = sort_of t = s orelse 
                raise ERR ("allE.sorts inconsistent",
                           [s,sort_of t],[mk_var(n,s),t],[])
    in
        thm(contl_U [G,fvt t],A,substf (ns,t) b)
    end

(**********************************************************************

A,Γ |- f[t/Var(a,s)]
------------------------------ existsI, require sort_of t = s, Var(t) ⊆ Γ
A,Γ |- ?a: s. f

Note: by induction, already have Var(s), Var(t) is subset of G? No, say 
when we want ?a:ob. TRUE from empty cont and assum list.

**********************************************************************)

fun existsI (a,s) t f (thm(G,A,C)) = 
    let 
        val _ = HOLset.isSubset(fvt t,G)
        val _ = sort_of t = s orelse 
                raise simple_fail"term and variable to be abstract of different sorts"
        val _ = eq_form (C, substf ((a,s),t) f) orelse
                raise ERR ("existsI.formula has the wrong form, should be something else: ",
                           [],[],[C,substf ((a,s),t) f])
    in
        thm(G,A,mk_exists a s (abstract (a,s) f))
    end


(**********************************************************************

X, Γ1 |- ?x. ϕ(x)        Y, ϕ(a),Γ2 ∪ {a:s0} |- B
-------------------------------------------------- existsE, requires a not in Y and not in B
X,Y, Γ1 ∪ Γ2 |- B

**********************************************************************)

local
    fun delete'(s,e) = HOLset.delete(s,e) handle _ => s 
in
fun existsE (a,s0) (thm(G1,A1,C1)) (thm(G2,A2,C2)) =
    let 
        val ((n,s),b) = dest_exists C1
        val _ = fmem (substf ((n,s),mk_var(a,s0)) b) A2
        val _ = s = s0 orelse 
                raise ERR ("the given variable has unexpected sort, should have another sort",[s,s0],[],[])
        val _ = (HOLset.member
                     (HOLset.union
                          (fvfl (ril (substf ((n,s),mk_var(a,s0)) b) A2),
                           fvf C2),(a,s0)) = false) orelse
                raise simple_fail "the given variable occurs unexpectedly"
    in
        thm(contl_U[G1,delete'(G2,(a,s0))],
            asml_U[A1,(ril (substf ((n,s),mk_var(a,s0)) b) A2)],C2)
    end
end

(**********************************************************************

input (?!a. ϕ(a))

phi a

fvf phi,[] |- (?!a. ϕ(a)) <=> ?a. ϕ(a) & !a'. ϕ(a') ==> a' = a

**********************************************************************)


fun uex_def f = 
    case view_form f of
        vQ("?!",n,s,b) => 
        let val n' = fst o dest_var o (pvariantt (fvf b)) $ mk_var(n^"'",s)
                                                          (*n ^ "'"*)
            val phia' = substf((n,s),mk_var(n',s)) b
            val impf = mk_imp phia' (mk_eq (mk_var(n',s)) (mk_var(n,s)))
            val allimpf = mk_forall n' s impf
            val rhs = mk_exists n s (mk_conj b allimpf)
        in
            mk_thm(fvf f,[],mk_dimp f rhs)
        end
      | _ => raise ERR ("uex_def.input is not a unique existence",[],[],[f])



fun refl t = thm (fvt t,[],mk_eq t t) 

fun sym th = 
    if is_eq (concl th) then 
        let 
            val (l,r) = dest_eq (concl th)
        in thm(cont th,ant th,mk_eq r l)
        end
    else raise ERR ("sym.not an equality: ",[],[],[concl th])

fun trans th1 th2 = 
    let 
        val _ = is_eq (concl th1) orelse 
                raise ERR ("trans.first thm not an equality: ",[],[],[concl th1])
        val _ = is_eq (concl th2) orelse
                raise ERR ("trans.second thm not an equality: ",[],[],[concl th2])
        val (t1,t2) = dest_eq (concl th1)
        val (t3,t4) = dest_eq (concl th2)
        val _ = t2 = t3 orelse
                raise ERR ("trans.equalities do not match",[],[],[concl th1,concl th2])
    in 
        thm(contl_U[cont th1,cont th2],
            asml_U[ant th1,ant th2],mk_eq t1 t4)
    end


(**********************************************************************

A, f1, Γ |- f2
-------------------- disch f1
A, Γ u Var(f1) |- f1 ==> f2

Note: do not require f1 in assumption, if not, add its variables into the context.

**********************************************************************)

fun disch f1 (thm(G,A,f2)) =
        thm (HOLset.union(G,fvf f1),ril f1 A,mk_imp f1 f2)

(**********************************************************************

A1, Γ1 |- A ==> B           A2, Γ2|- A
---------------------------------------- mp
A1 u A2, Γ1 u Γ2 |- B

**********************************************************************)


fun mp (thm (G1,A1,C1)) (thm (G2,A2,C2)) = 
    let
        val (A,B) = dest_imp C1
        val _ = eq_form(C2,A) orelse 
                raise ERR ("mp.no match",[],[],[C1,C2])
    in
        thm (contl_U [G1,G2],asml_U[A1,A2],B) 
    end


(**********************************************************************

A, Γ |- B
-------------------- add_cont Γ'
A, Γ u Γ' |- B

**********************************************************************)

fun add_cont nss th = thm(HOLset.union(cont th,nss),ant th,concl th)

fun check_wffv fvs = 
    case fvs of 
        [] => true
      | h :: t => if ill_formed_fv h then
                      raise ERR ("ill-formed free variable",[snd h],[mk_var h],[])
                  else check_wffv t

fun wffv_ok f = check_wffv (HOLset.listItems (fvf f))
  
(*
fun new_ax f = 
    let val _ = wffv_ok f orelse
                raise ERR ("formula contains ill-formed free variable(s)",[],[],[])
        val _ = HOLset.equal(fvf f,essps) orelse
                raise simple_fail"formula has free variables"
    in
        mk_thm(essps,[],f)
    end

*)

fun new_ax f = 
    let
        val _ = HOLset.equal(fvf f,essps) orelse
                raise simple_fail"formula has free variables"
    in
        mk_thm(essps,[],f)
    end



(*
fun all_distinct l = 
    case l of [] => true
            | h :: ts => if List.exists (fn t => eq_term(t,h)) ts then false
                         else true

fun no_ukn_psym f = HOLset.isEmpty (HOLset.filter (not o is_pred) (psymsf f))

fun no_ukn_fsym f = HOLset.isEmpty (HOLset.filter (not o is_fun) (fsymsf f))


(*will complain if the new pred is not currently stored in the dict*)


fun define_pred f = 
    let val fvs = fvf f
        val _ = HOLset.isEmpty fvs orelse 
                raise simple_fail
                      "formula has unexpected free variables"
        val (body,bvs) = strip_forall f 
        val (l,r) = dest_dimp body 
        val (P,args) = dest_pred l 
        val _ = List.all is_var args orelse raise simple_fail"input arguments is not a variable list"
        val _ = HOLset.isSubset (fvf r,fvf l) 
                orelse raise simple_fail"unexpected free variable on RHS"
      (*  val _ = case lookup_pred (psyms0) P of NONE => () | _ => raise simple_fail ("redefining predicate: " ^ P) *)
        val _ = all_distinct args orelse 
                raise simple_fail 
                      "input arguments are not all distinct"
        val _ = no_ukn_psym r orelse 
                raise simple_fail 
                      "RHS contains unknown predicate"
        val _ = no_ukn_fsym r orelse 
                raise simple_fail
                      "RHS contains unknown function"
        (*check P is a fresh name if not then fail*)
        (*check RHS variables are subset of LHS ones*)
        (*check arguments are all distinct*)
        (*store P in psymd*)
        val _ = new_pred P (List.map dest_var args)
    in mk_thm(essps,[],f)
    end 
(*check that R does not contain any unknown predicate symbols/fun syms*)

*)


fun mk_foralls nsl f = 
    case nsl of 
        [] => f
      | (h as (n,s)) :: t =>
        mk_forall n s (mk_foralls t f)

fun define_pred f = 
    let val fvs = fvf f
        val _ = HOLset.isEmpty fvs orelse 
                raise simple_fail
                      "formula has unexpected free variables"
        val (body,bvs) = strip_forall f 
        val (l,r) = dest_dimp body 
        val (P,args) = dest_fvar l 
        val _ = List.all is_var args orelse raise simple_fail"input arguments is not a variable list"
        val _ = HOLset.isSubset (fvf r,fvf l) 
                orelse raise simple_fail"unexpected free variable on RHS"
        val _ = new_pred P (List.map dest_var args)
        val l' = mk_pred P args
        val f' = mk_foralls bvs (mk_dimp l' r)
    in mk_thm(essps,[],f')
    end 




(*
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

*)




(*
fun define_fun f = 
    let val fvs = fvf f
        val _ = HOLset.isEmpty fvs orelse raise simple_fail"formula has unexpected free variables"
        val (body,bvs) = strip_forall f 
        val (l,r) = dest_eq body 
        val (nf,sf,args) = dest_fun l 
        val _ = List.all is_var args orelse raise simple_fail"input arguments is not a variable list"
        val _ = HOLset.isSubset (fvt r,fvt l) 
                orelse raise simple_fail"unexpected free variable on RHS"
       (* val _ = case lookup_fun fsyms0 nf of NONE => () | _ => raise simple_fail("redefining predicate: " ^ nf) *)
        val _ = all_distinct args orelse raise simple_fail"input arguments are not all distinct"
        val fsyms0 = new_fun nf (sf,(List.map dest_var args))
    in mk_thm(essps,[],f)
    end
*)




(*edit ex2fsym 1.!A B C. P(A,B,C) ==> ?Q.

2.deal with uex*)


fun new_ax f = 
    let
        val _ = HOLset.equal(fvf f,essps) orelse
                raise simple_fail"formula has free variables"
    in
        mk_thm(essps,[],f)
    end



fun define_fsym fsym vars th = 
    let val (ct,asl,con) = dest_thm th
        val (hyp,conc) = dest_imp con 
        val inputvars0 = filter_cont ct
        val inputvars = List.foldr (fn (s,e) => HOLset.add(e,s)) 
                                   essps vars
        val _ = HOLset.isSubset(inputvars0,inputvars) orelse 
                raise simple_fail "there are necessary input variables missing"
        val ((n,s),b) = dest_exists conc
        val _ = new_fun fsym (s,vars)
        val fterm = mk_fun fsym (List.map mk_var vars)
        val b' = substf ((n,s),fterm) b
    in mk_thm (ct,asl,mk_imp hyp b')
    end










exception UNCHANGED
 fun total f x = SOME (f x) handle e => NONE

fun MAP f l = 
   let
     (* map2 is the version where something has changed *)
     fun map2 A [] = List.rev A
       | map2 A (h::t) = map2 ((f h handle e => h) :: A) t
     (* map1 is the version to call where nothing has changed yet *)
     fun map1 n [] = raise UNCHANGED
       | map1 n (h::t) = 
           case total f h of
             SOME fh => map2 (fh::(rev $ List.take(l,n))) t
           | NONE => map1 (n + 1) t
   in
     map1 0 l
   end


fun fVar_Inst_th (pair as (P,(argl:(string * sort) list,Q0))) th = 
    let val (ct,asl,w) = dest_thm th
        val lcs = List.foldr
                      (fn (ns,nss) => HOLset.delete(nss,ns)
                                      handle _ => nss) 
                      (fvf Q0) argl
        val ct' = HOLset.union(ct,lcs)
        val aslw' = MAP (fVar_Inst_f pair) (w :: asl)
    in mk_thm (ct',tl aslw',hd aslw')
    end




fun define_fsym (fname,vl) t = 
    let val st = sort_of t
        val _ = new_fun fname (st, vl)
        val ft = mk_fun fname (List.map mk_var vl)
        (*check vl is subset of vars in t*)
        val inputvset = List.foldr
                            (fn(a,s) => HOLset.union(s,fvt (mk_var a))) essps vl
        val _ = HOLset.isSubset(fvt t,inputvset) orelse 
                raise simple_fail "define_fsym.input contains extra variable(s)"
        val f = mk_eq ft t
        val ct = fvf f
    in mk_thm (ct,[],f)
    end


 
fun define_psym (pname,vl) f = 
    let 
        val _ = new_pred pname vl
        val pfm = mk_pred pname (List.map mk_var vl)
        val fm = mk_dimp pfm f
        val _ = HOLset.isSubset(fvf f,fvf pfm) orelse 
                raise simple_fail "define_psym.input contains extra variable(s)"
        val ct = fvf fm
    in mk_thm (ct,[],fm)
    end

(*once proved existence of input terms can make sure the term of current sort exists, can have antecedent in th

eth: {A,B,f:A->B},[] |- ?a:st(H).T
fname: "fun"
vl  [‘f:A->B’]
th {A,B,f:A->B,g:K->M} |- ?a:st(H). P(a)

f:1->0 |- ?

{A,B,f:A->B,g:K->M} |- ?!a:st(H). P(a,f,g)



A * B isPr(p1,p2)

|- !(A : set)  (B : set).
        (!(x : mem(A#)). ?(y : mem(B#)). P(x#, y#)) ==>
        ?(f : fun(A#, B#)). !(a : mem(A#)). P(a#, App(f#, a#)): thm


!A B. ?AB. isPr(AB,A,B)

A 

without axiom of choice, function symbols can only abbrev existing actual function applid

*)

(*
fun SKOLEM eth fname vl th = 
    let val asm = ant th
        val c = concl th
        val ((n,s),b) = dest_exists c
        val c0 = concl eth
        val _ = HOLset.isSubset(cont eth,cont th) orelse
                raise ERR ("SKOLEM.eth has extra variables",
                           [],[],[])
        val _ = eq_forml (ant eth) [] orelse
                raise ERR ("SKOLEM.eth has assumptions",
                           [],[],[])
        val _ = eq_form(concl eth, mk_exists n s TRUE)
                orelse 
                raise ERR ("SKOLEM.ill-formed eth",[],[],[c0])
        val _ = new_fun fname (s,vl)
        val inputvars0 = filter_cont (cont th)
        val inputvars = List.foldr (fn (s,e) => HOLset.add(e,s)) 
                                   essps vl
        val _ = HOLset.isSubset(inputvars0,inputvars) orelse 
                raise simple_fail "there are necessary input variables missing"
        val fntm = mk_fun fname (List.map mk_var vl)
        val b' = substf ((n,s),fntm) b
    in mk_thm(cont th,ant th,b')
    end
*)


(*

what should be the rule if also want it to deal with 
no free var

[v1,...,vn] |- ?a:srt(v1,...,vn);. T


[v1,...,vn,...,v_{n + m}], A1,...An |- ?!_{R}a. P(a)


input 3: a theorem on R.

output

[v1,...,vn,...,v_{n + m}], A1,...An 
|- P(f(filtered{v1,...,v_{n + m}})) &
   (f() is up to R)

[A,B,f:A->B]


?a. P(a) & !a'. P(a') ==> R(a,a')


SKOLEM



f:A->B

f'(a:1->A) = b:1->B

f o a:1->B

ordinals in SEAR

existence of a function takes an ordinal, and gives the least ordinal of strictly greater card.

csucc(α) = sup{β | β is in bijection with a and β is also an aordinal}

Exists a type of 

*)

end
