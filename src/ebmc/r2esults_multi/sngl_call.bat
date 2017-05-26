#!/usr/bin/tcsh
limit cputime $1
#printf "$1 $2 $3\n" > $2_p$3.prot
printf "exmp $2 prop. $3 " >> res.txt

#../ebmc $2.sv --ic3 --property main.property.$3  > $2_p$3.prot
../ebmc $2.sv --ic3 --property main.property.$3  --constr > $2_p$3.prt

#printf "no constr: " >> res.txt
#grep property $2_p$3.prot | tr -d '\n' >> res.txt
printf ", with constr: " >> res.txt
grep property $2_p$3.prt >> res.txt
