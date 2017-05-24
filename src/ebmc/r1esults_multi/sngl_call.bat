#!/usr/bin/tcsh
limit cputime $1
#printf "$1 $2 $3\n" > $2_p$3.prot
printf "exmp $2 prop. $3 " >> res.txt
../ebmc $2.sv --ic3 --constr --property $2.property.$3  > $2_p$3.prot
grep property $2_p$3.prot >> res.txt
