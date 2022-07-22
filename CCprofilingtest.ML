fun usestuff () = 
    (use "CCAFmaster.ML";
     use "CCAFsettings.sml");

PolyML.Profiling.profile PolyML.Profiling.ProfileTime usestuff ();
