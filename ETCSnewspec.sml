
val areqeqvth = proved_th $
e0
(rpt strip_tac >> arw[])
(form_goal “∀A B. (!i:A->B. i = i) &
 (!i:A->B i':A->B. i = i' ==> i' = i) &
 (!i:A->B i':A->B i'':A->B. 
   i = i' & i' = i'' ==> i = i'')”)




fun uex_spec fname vl eth uexth0 = 
    let 
        val ((_,st),_) = dest_uex (concl uexth0)
        val stn = st |> dest_sort |> #1
        val dependson = st |> dest_sort |> #2 
        val eqvth = if stn = "ar" then areqeqvth |> specl dependson else
                    raise simple_fail "uex_spec.ill-formed sort"
        val uexth = uex_expand' uexth0
        val (arg,Q) = dest_uex (concl uexth0)
        val argQ = ([arg],Q)
        val arg' = dest_var (pvariantt (fvf Q) (mk_var arg)) 
        val equality = mk_eq (mk_var arg) (mk_var arg') 
        val arg12eqr = ([arg],[arg'],equality) 
    in new_spec argQ arg12eqr [fname] vl eth eqvth uexth
    end

fun quex_spec fname qvl eth uexth0 = 
    let val tl = List.map (qparse_term_with_cont (cont uexth0)) qvl 
        val vl = List.map dest_var tl
    in uex_spec fname vl eth uexth0
    end

fun simple_uex_spec fname vl uexth0 = 
    let val uexth = uex_expand' uexth0
        val eth0 = ex_P_ex (concl uexth)
        val eth = mp eth0 uexth
    in uex_spec fname vl eth uexth0 
    end


fun qsimple_uex_spec fname qvl uexth0 = 
    let val tl = List.map (qparse_term_with_cont (cont uexth0)) qvl 
        val vl = List.map dest_var tl
    in simple_uex_spec fname vl uexth0
    end
