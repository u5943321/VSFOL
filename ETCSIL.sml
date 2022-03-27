
val IMP_ex = prove_store("IMP_ex",
e0
(cheat)
(form_goal 
“?imp: (1+1) * (1+1) -> 1+1. 
 !p1 p2. imp o Pa(p1,p2) = TRUE <=> (p1 = TRUE ==> p2 = TRUE)”));

rastt "a:(1 + 1 ->A) o (imp : 2 * 2 -> 2)"



val _ = new_fun "2" (ob_sort,[])

val _ = new_abbr ("+",[ONE,ONE])  ("2",[]) 
