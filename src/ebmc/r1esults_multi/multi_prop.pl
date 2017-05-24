#!/usr/bin/perl

if ($#ARGV == -1) {
  printf("multi_prop.pl exmps\n");
  exit(0);
}


qx(rm -f res.txt);
qx(rm -f *.prot);

$exmp_path = "/home/eugene/e0xamples/hwmcc11/multi";

(my $fname) = @ARGV;

$time_limit = 800;

open EXMPS,"< $fname" or die "failed to open file $fname\n";

while (<EXMPS>) {
  chomp($_);
  $exmp = $_;  

  @words = split / /,$exmp;

 # print "@words";

  $name = $words[0];

  printf "$name\n";

  qx(cp $exmp_path/$name.aig .);
  qx(ba2ver $name.aig $name.sv pa);
 

  $i = 0;
  foreach (@words)  {
   $i++;
   if ($i == 1) {next;}
   printf("   prop. $_\n");
   qx(sngl_call.bat $time_limit $name $_);
  }

#  printf("%s\n",$num_prop);

  qx(rm -f $name.aig $name.sv $name.sv.cnstr);
}

close EXMPS;

$answer = qx(diff -s res.txt rpnt.txt);
printf "$answer";
