
use "newspec.sml";
use "CCAFsorts.sml";
use "CCAFnewspec.sml";
use "CCAFsetting.sml";
use "adj.sml";
use "duals.sml";
use "discrete.sml";
use "Pb_def.sml";
use "Icat_def.sml";
use "Thm24.sml";
use "isio_def.sml";
use "ISC.sml";

(*
All files about CCAF serves for proving theorems from McLarty's original paper.
setting: Theorem 1-17, except for Theorem 13.

adj: About adjunction (Theorem 13).

duals: opposite/dual categories. Axiomatised in a different way from McLarty to  fit into the logic better (Theorem 18-19).

discrete: Discrete categories (Theorem 20-23).

Pb_def: construct the function symbols Pbo, Pba1 and Pba2 using specification rule. 

Icat_def: definition of internal category according to MacLane's "Categories for working mathematician".

Thm24: Theorem 24.

isio_def: use the predicate "isio" to give `semantical` version of the diagrams in the definition of internal category and internal functors.

ISC. Internal small category (Theorem 25-26). 
*)
