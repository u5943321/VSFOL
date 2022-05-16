
val AX5 = store_ax("AX5",
“!A.?B p:B->A Y M:B~>Y.  
 (!b Mb.
     (?i:Mb->Y. Inj(i) & 
                !y. (?y0. App(i,y0) = y) <=> Holds(M,b,y))
     ==> P(App(p,b),Mb)) & 
 !a:mem(A) X. P(a,X) ==> ?b. App(p,b) = a”)

