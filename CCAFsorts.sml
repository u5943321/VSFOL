

val _ = new_sort "cat" [];

val _ = new_sort "fun" [("A",mk_sort "cat" []),("B",mk_sort "cat" [])]

val _ = new_sort_infix "fun" "->"

val cat_sort = mk_sort "cat" []
fun fun_sort A B = mk_sort "fun" [A,B]
fun mk_cat A = mk_var(A,cat_sort)
fun mk_func F A B = mk_var(F,fun_sort A B)

val _ = EqSorts := "fun" :: (!EqSorts)

 (*

val _ = new_sort "nt" [("f",fun_sort (mk_cat "A") (mk_cat "B")),
                       ("g",fun_sort (mk_cat "A") (mk_cat "B"))]
*)

val _ = new_fun "o" (mk_sort "fun" [mk_var("A",mk_sort "cat" []),mk_var("C",mk_sort "cat" [])],[("f",mk_sort "fun" [mk_var("B",mk_sort "cat" []),mk_var("C",mk_sort "cat" [])]),("g",mk_sort "fun" [mk_var("A",mk_sort "cat" []),mk_var("B",mk_sort "cat" [])])])

 
