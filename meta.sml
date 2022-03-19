
(*Fragment which is necessary if we want to use one theory to say something about the meta theory of another theory*)

datatype workspace = WS of sort list

isTopos(C) <=> hasProd(C) & hasEq(C) ...



hasProd(C) <=> !A:Ob(C) B. ?AB p1:AB ->A. !f:X:Ob(C) ->A g:X->B. 
?!fg:X->AB. p1 o fg = f & p2 o fg = g 


output is 

Ob(C) |-> ob

Ar(A:Ob(C),B:Ob(C)) |-> ar(A,B)


hasProd*(ws) <=> !A:

Russel's paradox:

?a:set. !e:set. IN(e,a) <=> ~(IN(e,e))

IN(a,a) <=> ~IN(a,a)

not enough sorts distinguish.


?a: sort. 


!a:ds(A). ?


type of all types are 

fun inst_ws f assi = 
    case f of 


“?C:Cat. !A:Ob(C).?A0:”


Is that the fact that if I never use comprehensionin the same sort, then I never get intto Russel paradox.


have a definition in NBG of topspace, Define a sheaf.


form the category of sets:

?C. !A:Ob(C). ?!A0:set. Comefrom(A,A0)




Type of all types: being able to use property of type to reasoning about the whole thing contains all types.
