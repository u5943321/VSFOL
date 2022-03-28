

(*internal logic via truth table:

Conj: T T
DISJ

*)
val IMP_ex = prove_store("IMP_ex",
e0
(cheat)
(form_goal 
“?imp: (1+1) * (1+1) -> 1+1. 
 !p1 p2. imp o Pa(p1,p2) = TRUE <=> (p1 = TRUE ==> p2 = TRUE)”));



(*

val _ = new_fun "2" (ob_sort,[])

val _ = new_abbr ("+",[ONE,ONE])  ("2",[]) 

rastt "a:(1 + 1 ->A) o (imp : 2 * 2 -> 2)" problem

need a function subst_ast which subst aId"2" into "1 + 1"

*)
