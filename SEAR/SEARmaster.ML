val mydir = OS.FileSys.getDir();
val kerneldir = "..";
val _ = OS.FileSys.chDir kerneldir;
use "master.ML";
val _ = OS.FileSys.chDir mydir;

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

