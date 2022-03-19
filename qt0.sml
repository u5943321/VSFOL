(*Relational image*)
val Sg_ex = prove_store("Sg_ex",
e0
(cheat)
(form_goal “!A. ?Sg:A-> Pow(A). 
 !a a'.IN(a',App(Sg,a)) <=> a' = a”));

val Sg_def = Sg_ex |> spec_all |> ex2fsym0 "Sg" ["A"] 
                   |> gen_all


val Sing_ex = prove_store("Sing_ex",
e0
(cheat)
(form_goal
 “!A a:mem(A).?sa. sa = App(Sg(A),a)”));

val Sing_def = Sing_ex |> spec_all |> ex2fsym0 "Sing" ["a"]

val Ri_ex = prove_store("Ri_ex",
e0
(cheat)
(form_goal “!A B r:A~>B. ?Ri:Pow(A) -> Pow(B).
 !s b. IN(b,App(Ri,s)) <=> ?a. IN(a,s) & Holds(r,a,b)”));

val Ri_def = Ri_ex |> spec_all |> ex2fsym0 "Ri" ["r"] |> gen_all

(*Relational singleton image*)
val Rsi_ex = prove_store("Rsi_ex",
e0
(cheat)
(form_goal “!A B r:A~>B. ?rsi. rsi = o1(Ri(r),Sg(A))”));

val Rsi_def = Rsi_ex |> spec_all |> ex2fsym0 "Rsi" ["r"]
                     |> gen_all


val rsi_ex = prove_store("rsi_ex",
e0
(cheat)
(form_goal “!A B r:A~>B a. ?s. s = App(Rsi(r),a)”));

val rsi_def = rsi_ex |> spec_all |> ex2fsym0 "rsi" ["r","a"]
                     |> gen_all


val IMAGE_ex = prove_store("IMAGE_ex",
e0
cheat
(form_goal “!A B f: A -> B s0:mem(Pow(A)). ?im:mem(Pow(B)). 
  (!b. IN(b,im) <=> ?a. IN(a,s0) & b = App(f,a))”));

val IMAGE_def = IMAGE_ex |> spec_all |> ex2fsym0 "IMAGE" ["f","s0"]
                   |> gen_all




val respects_def = define_pred
“!A B f:A->B r:A~>A. respects(f,r) <=> 
 (!y z.Holds(r,y,z) ==> App(f,y) = App(f,z))”


val congruent2_def = define_pred
“!A r1:A~>A B r2:B~>B C f:A * B -> C.
 congruent2(r1,r2,f) <=> 
 !x y. Holds(r1,x,y) ==> !u v.Holds(r2,u,v) ==>
 App(f,Pair(x,u)) = App(f,Pair(y,v))”


val respects2_def = define_pred 
“!A B f:A * A->B r:A~>A. respects2(f,r) <=> 
 congruent2(r,r,f)”

(*need to automatic define function together with its applied function symbol*)

(*
val lp_lemma = prove_store("lp_lemma",
e0
(cheat)
(form_goal
 “!A B f:A->Pow(B) a:mem(A) c. 
 (!y:mem(A). App(f,y) = c) ==> IMAGE(f = c”));
*)

val cong_lemma = prove_store("lp_lemma",
e0
(cheat)
(form_goal
 “!A B f:A-> B s:mem(Pow(A)). 
  (~(s = Empty(A))) ==>
  !b. (!a. IN(a,s) ==> App(f,a) = b) ==> 
  IMAGE(f,s) = Sing(b)”));


val UN_equiv_class = prove_store("UN_equiv_class",
e0
(cheat)
(form_goal
 “!A r:A~>A. ER(r) ==> !B f:A->B. respects(f,r) ==>
  !a.IMAGE(f,rsi(r,a)) = Sing(App(f,a))”));

val sPair_ex = prove_store("sPair_ex",
e0
(cheat)
(form_goal
 “!A B. ?sp:Pow(A) * Pow(B) -> Pow(A * B). 
   !s1 s2 ab. IN(ab,App(sp,Pair(s1,s2))) <=> 
   IN(Fst(ab),s1) & IN(Snd(ab),s2) ”));

val sPair_def = sPair_ex |> spec_all 
                         |> ex2fsym0 "sPair" ["A","B"]
                         |> gen_all

val spair_ex = prove_store("spair_ex",
e0
(cheat)
(form_goal “!A B s1 s2. ?s. s = App(sPair(A,B),Pair(s1,s2))”));

val spair_def = spair_ex |> spec_all |> ex2fsym0 "spair" ["s1","s2"] |> gen_all

val R_CROSS_ex = prove_store("R_CROSS_ex",
e0
(cheat)
(form_goal
 “!A r1:A~>A B r2:B~>B. 
  ?r3:A * B ~> A * B. 
   (!a b a' b'. Holds(r3,Pair(a,b),Pair(a',b')) <=> 
    Holds(r1,a,a') & Holds(r2,b,b'))”));

val R_CROSS_def = R_CROSS_ex |> spec_all |> ex2fsym0 "RC"
                             ["r1","r2"] |> gen_all



val ER_CROSS_ER = prove_store("ER_CROSS_ER",
e0
(rw[ER_def] >> rpt strip_tac 
 >-- (fs[Refl_def] >> strip_tac >>
     qsspecl_then [‘a’] strip_assume_tac Pair_has_comp >>
     arw[])
 >-- (fs[Sym_def] >> rpt strip_tac >>
     qsspecl_then [‘a1’] strip_assume_tac Pair_has_comp >>
     qsspecl_then [‘a2’] strip_assume_tac Pair_has_comp >>
     fs[] >> rfs[] >> strip_tac >> 
     first_x_assum irule >> arw[]) >>
 fs[Trans_def] >> rpt strip_tac >>
 qsspecl_then [‘a1’] strip_assume_tac Pair_has_comp >>
 qsspecl_then [‘a2’] strip_assume_tac Pair_has_comp >>
 qsspecl_then [‘a3’] strip_assume_tac Pair_has_comp >>
 fs[] >> rfs[] >> strip_tac >> first_x_assum irule
 >-- (qexists_tac ‘a'’ >> arw[]) >>
 qexists_tac ‘b'’ >> arw[])
(form_goal
 “!A r1:A~>A. ER(r1) ==> !B r2:B ~>B. ER(r2) ==>
  (!r3:A * B ~> A * B. 
   (!a b a' b'. Holds(r3,Pair(a,b),Pair(a',b')) <=> 
    Holds(r1,a,a') & Holds(r2,b,b')) ==> 
  ER(r3))”));


val rsi_property = prove_store("rsi_property",
e0
(cheat)
(form_goal
 “!A B r:A ~> B a a0. IN(a0,rsi(r,a)) <=> Holds(r,a,a0)”));


val congruent2_RC = prove_store("congruent2_RC",
e0
(rw[congruent2_def,respects_def] >> dimp_tac >>
rpt strip_tac (* 2 *)
>-- (qsspecl_then [‘z’] strip_assume_tac Pair_has_comp >>
     qsspecl_then [‘y’] strip_assume_tac Pair_has_comp >>
     arw[] >> first_x_assum irule >> fs[R_CROSS_def]) >>
first_x_assum irule >> rw[R_CROSS_def] >> arw[])
(form_goal “congruent2(r1:A~>A,r2:B~>B,f:A* B->C) <=> respects(f,RC(r1,r2))”));

val spair_RC = prove_store("spair_RC",
e0
(rpt strip_tac >> rw[spair_def] >> irule IN_EXT >>
strip_tac >> rw[sPair_def,rsi_property] >>
qsspecl_then [‘x’] strip_assume_tac Pair_has_comp >>
arw[] >> rw[Pair_def',R_CROSS_def])
(form_goal
“!A r1:A~>A B r2: B~> B a1 a2.spair(rsi(r1:A ~> A, a1), rsi(r2:B~>B, a2)) = rsi(RC(r1, r2), Pair(a1, a2))”));

val UN_equiv_class2 = prove_store("UN_equiv_class2",
e0
(rpt strip_tac >>
 qby_tac ‘ER(RC(r,r))’ >-- cheat >>
 drule UN_equiv_class >> 
 qby_tac ‘respects(f,RC(r,r))’ >-- cheat >>
 first_x_assum drule >>
 first_x_assum (qspecl_then [‘Pair(a1,a2)’] assume_tac) >>
 qsuff_tac
 ‘spair(rsi(r, a1), rsi(r, a2)) = rsi(RC(r, r), Pair(a1, a2))’
 >-- (strip_tac >> arw[]) >>
 rw[spair_RC])
(form_goal
 “!A r:A~>A. ER(r) ==> !B f:A * A->B. respects2(f,r) ==>
  !a1 a2.IMAGE(f,spair(rsi(r,a1),rsi(r,a2))) = Sing(App(f,Pair(a1,a2)))”));


(*extra condition not evil because everyone else also assumed the equiv class is non empty since the rep function in their version if Q -> A*)

(*
val QUOTIENT_def = define_pred
“!A R:A~>A Q abs:A->Q rep:Q->Pow(A).
 QUOTIENT(R:A ~> A,abs:A ->Q ,rep) <=> 
 (!q. ?a. IN(a,App(rep,q))) & 
 (!q:mem(Q) a. IN(a,App(rep,q)) <=>  App(abs,a) = q) &
 (!q:mem(Q) a1 a2. IN(a1,App(rep,q)) & IN(a2,App(rep,q)) ==>
   Holds(R,a1,a2)) &
 (!r:mem(A) s.Holds(R,r,s) <=> 
  Holds(R,r,r) & Holds(R,s,s) & (App(abs,r) = App(abs,s)))”
*)


val Whole_ex =  prove_store("Whole_ex",
e0
(cheat)
(form_goal “!A. ?s:mem(Pow(A)). (!a:mem(A). IN(a,s))”));

val Whole_def = Whole_ex |> spec_all |> ex2fsym0 "Whole" ["A"] |> gen_all 


val Cls_ex = prove_store("Cls_ex",
e0
(cheat)
(form_goal
 “!A R:A~>A.?s. s = IMAGE(Rsi(R),Whole(A))”));

(*qdefine_fsym ("Cls",[‘R:A~>A’]) ‘IMAGE(Rsi(R),Whole(A))’*)


fun define_fsym (fname,vl) t = 
    let val st = sort_of t
        val _ = new_fun fname (st, vl)
        val ft = mk_fun fname (List.map mk_var vl)
        val f = mk_eq ft t
        val ct = fvf f
    in mk_thm (ct,[],f)
    end


 
fun define_psym (pname,vl) f = 
    let 
        val _ = new_pred pname vl
        val pfm = mk_pred pname (List.map mk_var vl)
        val fm = mk_dimp pfm f
        val ct = fvf fm
    in mk_thm (ct,[],f)
    end

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

(*so define_fsym can only define new function symbols with old function symbols, it is impossible to create a function symbol which takes a:A->B to an arrow B->A, unless this is supported by orginal axioms.
user should not get access to new_fsym and new_pred
*)

        



(*
theorem eq equiv class iff: "[equiv A r; x ∈ A; y ∈ A]
=⇒ (r‘‘{x} = r‘‘{y}) = ((x,y) ∈ r)"

*)

val eq_equiv_class_iff = prove_store("eq_equiv_class_iff",
e0
(rw[ER_def,Refl_def,Sym_def,Trans_def] >> cheat
 )
(form_goal 
 “!A r:A~>A. ER(r) ==> !x y. rsi(r,x) = rsi(r,y) <=> Holds(r,x,y)”));


(*next step: form the quotient set Cls as a set, Thm_2_4*)

val Injf_def = qdefine_psym ("Injf",[‘f:A->B’])
‘!a1 a2. App(f,a1) = App(f,a2) ==> a1 = a2’

val Thm_2_4_fun = prove_store("Thm_2_4_fun",
e0
(cheat)
(form_goal
 “!A.?B i:B->A. isInjf(i) & 
  !a:mem(A).P(a) <=> ?b. a = App(i,b)”));

val isRep_def = qdefine_psym ("isRep",[‘R:A~>A’,‘Rrep:Q -> Pow(A)’])
‘Injf(Rrep) & 
 !cl. (?a. cl = rsi(R:A~>A,a)) <=> (?q:mem(Q). App(Rrep,q) = cl)’ 


val isRep_ex = prove_store("isRep_ex",
e0
(cheat)
(form_goal
 “!A R:A~>A. 
  ?Q Rrep:Q-> Pow(A). isRep(R,Rrep)”));

(*for each relation, regardless ER or not at least yet, let the user provide the constant relation they define, and give the quotient set Q a name, so does the rep function Rrep.*)


(*for every function respects to R, define a function for the quotient version*)

“!f:R * A -> R. ”



(*
val _ = new_pred "QUOTIENT" 
(List.map (dest_var o rastt) ["R:A~>A","abs:Pow(A) ->Q","rep:Q -> Pow(A)"])

val QUOTIENT_def = store_ax("QUOTIENT_def",
“!A R:A~>A Q abs:Pow(A)->Q rep:Q->Pow(A).
 QUOTIENT(R:A ~> A,abs ,rep) <=> 
 (!q.App(abs,App(rep,q)) = q) &
 (!q:mem(Q) a1 a2. IN(a1,App(rep,q)) & IN(a2,App(rep,q)) ==>
   Holds(R,a1,a2)) &
 (!r:mem(A) s.Holds(R,r,s) <=> 
  Holds(R,r,r) & Holds(R,s,s) & 
  (App(abs,rsi(R,r)) = App(abs,rsi(R,s))))”);


*)

(*
val QUOTIENT_def =
    Define
      `QUOTIENT R abs rep <=>
        (!a:'b. abs (rep a) = a) /\
        (!a. R (rep a) (rep a)) /\
        (!(r:'a) (s:'a). R r s <=> R r r /\ R s s /\ (abs r = abs s))`;
*)


val quotient_rep_ex = prove_store("quotient_rep_ex",
e0
(rw[QUOTIENT_def] >> rpt strip_tac >>
 last_x_assum (qspecl_then [‘q’] strip_assume_tac) >>
 first_x_assum (drule o iffLR) >>
 qexists_tac ‘a’ >> arw[])
(form_goal
 “!A R:A~>A Q abs:A->Q rep:Q->Pow(A).
  QUOTIENT(R,abs,rep) ==> 
  !q:mem(Q). ?a. App(abs,a) = q”));


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




fun total f x = 
  SOME (f x) handle _ => NONE

fun PULL_CONJ p f = 
  if p f then SOME (frefl f)
  else
    case view_form f of
      Conn("&", [f1,f2]) => 
       (case total (PULL_CONJ p) f1 of
          NONE => (case total (PULL_CONJ p) f2 of
                     NONE => NONE
                   | SOME f2eqth => ...** )
        | SOME f1eqth => *...)
    | _ => NONE

       
