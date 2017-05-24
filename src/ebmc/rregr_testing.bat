#
rrm -f $1/*.prot
rrm -f $1/ *.prt
pproc_all.bat b1uggy.solved
pproc_all.bat corr.solved
pproc_all.bat u5nsolved
cd r0esults
diff -s b1uggy.solved.prot b1uggy.solved.rpnt
diff -s corr.solved.prot corr.solved.rpnt
diff -s u5nsolved.prot u5nsolved.rpnt
cd ..
 
