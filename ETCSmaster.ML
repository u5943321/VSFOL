(*use "master.ML";
use "ETCSsettings.sml";
use "ETCSN.sml";
use "ETCSFinite.sml";
use "ETCSL.sml";
use "ETCSZ.sml"; 
*)


use "newspec.sml";
use "ETCSsorts.sml";
use "ETCSnewspec.sml";
use "ETCSsettings.sml";
use "ETCSN'.sml";
use "ETCSFinite'.sml";
use "ETCSL.sml";
use "ETCSZ'.sml"; 

(*
  ETCSsettings:
  all the non-meta theorems in Lawvere's original paper 
  "AN ELEMENTARY THEORY OF THE CATEGORY OF SETS (LONG VERSION) WITH COMMENTARY"
  can be viewed at: https://artscimedia.case.edu/wp-content/uploads/2013/07/14182623/Lawvere-ETCS.pdf
  This file also contain on very elemantary set theory, which serves for the constructions onwards.
  Properties of internal logic operators are also proved here. 

  More theorems are proved in the SEAR counterpart of the files below, but the proofs would be easy to edit into an ETCS version.
  There are instances of application of internal logic in all the files below.

  ETCSN:
  Natural numbers in ETCS. 
  The theorem with name "SoE_lemma_2_5_5", saying that the inclusion 0 and SUC form a coproduct, is lemma 2.5.5 from Johnstone's textbook "Sketch of an Elephant".

  ETCSZ:
  Integers in ETCS, constructed from quotienting the object N * N.

  ETCSFinite:
  Finite sets.

  ETCSL:
  Lists in ETCS, constructed by induction. 
*)
