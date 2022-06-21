val _ = new_sort "ob" [] 
val _ = new_sort "ar" [("A",mk_sort "ob" []),("B",mk_sort "ob" [])];
val _ = EqSorts := "ar" :: (!EqSorts);
val _ = new_sort_infix "ar" "->";
val ob_sort = mk_sort "ob" [];
fun ar_sort A B = mk_sort "ar" [A,B];


fun mk_ob name = mk_var (name,ob_sort);
fun mk_ar name dom cod = mk_var (name,ar_sort dom cod);
