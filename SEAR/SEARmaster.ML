fun use s =
  (print ("******\n\nLoading SEAR file " ^ s ^ "\n\n******\n"); QUse.use s);
use "SEARsorts.sml";
use "SEARnewspec.sml";
use "SEARrel.sml";
use "SEARfun.sml";
use "SEARsetting.sml";
use "SEARpred_set.sml";
use "SEARNarith.sml";
use "ztest.sml";
use "SEARFiniteness.sml";
use "SEARList.sml";
use "fm.sml";
use "SEARUF.sml";
use "SEARrecty.sml";
use "SEARllist.sml";
use "SEARGrp.sml";
use "SEARexamplecol.sml";

(*
setting: Theorems inn the nlab page of SEAR, the original statements can be viewed at: https://ncatlab.org/nlab/show/SEAR . 
pred_set: elementary set theory in SEAR. 
Narith: Natural number arithmetic.
Zarith: Integer arithmetic, we prove theorems up to division with reminder.
Finitness: Finite sets.
List: List set. We defined El using the same approach as in HOL, and showed that we can define function over lists such as Map with correct behaviour using list induction.
fm: modal formulas.
UF: ultrafilters.
recty: modal logic.
llist: lazy lists. We defined LMap and proved it behaves correctly by corecursion and coinduction.
Grp: group theory, with usual DTT approach.
examplecol: existence of large sets.

*)
