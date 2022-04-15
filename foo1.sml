

fun part_match (fpartfn:form->form) th f = 
    let 
        val thf = fpartfn (#1 (strip_forall (concl th)))
        val fvd = match_form (fvfl (ant th)) (fVarsl (ant th)) 
                             thf f mempty
    in 
        inst_thm fvd th
    end

(* m f k t
 f := f 
 k := ?
 t := fm
*)

fun m (ttac:thm_tactic) ith rth f k fm g = 
    let val th0 = part_match f ith fm
        val th = rewr_rule[rth] th0
    in ttac th g
    end
    handle _ => k()

 
val conj1 = #1 o dest_conj
val conj2 = #2 o dest_conj

val strip_conj =
   let
      fun aux acc f =
         aux (aux acc (conj2 f)) (conj1 f)
         handle _ => f :: acc
   in
      aux []
   end


fun conj f t = t |> dest_imp |> #1 |> strip_conj |> f
fun max ith = ith |> concl |> strip_forall |> #1 |> conj length
 

(*mp_then with only Any *)
fun mp_then ttac ith0 rth (g as (ct,asl,w)) = 
    let val ith = ir_canon ith0
        val f = concl rth
        fun doit (n:int) =
            if n > max ith then raise simple_fail "doit"
            else m ttac ith rth (conj (el n)) (fn _ => doit (n + 1)) f g
    in doit 1
    end


fun m (ttac:thm_tactic) ith rth ff k fm g = 
    let val th0 = part_match ff ith fm
        val th = rewr_rule[rth] th0
    in ttac th g
    end
    handle _ => k()

val fpartfn = ff 
val th = ith
val f = fm


val fm = f
val ff = conj (el n)
m ttac ith rth 

val n = 1
m ttac ith rth (conj (el n)) (fn _ => doit (n + 1)) f g

fun dGEN (sel:thm_tactic -> tactic) k = sel o (mp_then k)

fun drule_then k = dGEN first_assum k

val drule = first_assum o (mp_then mp_tac)

val drule = dGEN first_assum mp_tac

val th0 = proved_th $
e0
cheat
(form_goal “P(a) ==>?b.P(b)”) 

val ttac = mp_tac
val ith0 = th0
val rth = assume “?a.P(a)”

val g = cg $
e0
(disch_tac)
(form_goal “(?a.P(a)) ==> ?b. P(b)”)

disch_tac >> disch_tac >>
first_x_assum drule 
“(A ==> B & C) ==> A ==> B & C”

first_x_assum (drule_then strip_assume_tac)

goal_assum (first_assum o mp_then mp_tac)





first_x_assum mp_then
