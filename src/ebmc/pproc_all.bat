#
limit cputime 65 
limit vmemoryuse 2800 megabytes
set bench_dir = /home/eugene/e0xamples/hwmcc10

rrm -rf r0esults/$1.prot

foreach file (`cat $1`)	
	
printf "--------------\n"
printf  "$file ::\n"


ccp $bench_dir/$file.aig r0esults
cd r0esults
ba2ver $file.aig $file.sv

printf "%s: " $file >> $1.prot
time ../ebmc $file.sv --ic3 >& $file.prt
set stat_var = $status
if ($stat_var >= 100) then
printf "unconventional termination\n" >> $1.prot
cd ..
continue
endif
if ($stat_var > 10) then
@ stat_var0 = $stat_var - 10
else
@ stat_var0 = $stat_var
endif
if ($stat_var0 == 0) then
printf "unsolved\n"
else if ($stat_var0 == 1) then
printf "$file result: bug is found\n" 
printf "bug is found" >> $1.prot
if ($stat_var > 10) then 
printf " : verification failed\n" >> $1.prot
else 
printf "\n" >> $1.prot
endif
else if ($stat_var0 == 2) then
printf "$file result: fixed point is reached\n"
printf "property holds" >> $1.prot
if ($stat_var > 10) then
printf " : verification failed\n" >> $1.prot
else 
printf "\n" >> $1.prot
endif
else if ($stat_var0 == 3) then
printf "not finished\n" >> $1.prot
printf "$file result: time exceeded\n"
else if ($stat_var0 == 4) then
printf "not finished\n" >> $1.prot
printf "$file result: memory exceeded\n"
else  printf "not finished\n" >> $1.prot
endif
rrm -f $file.aig
rrm -f $file.sv
#r1em.bat $file
cd ..
end


