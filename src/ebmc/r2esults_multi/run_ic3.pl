#!/usr/bin/perl

if ($#ARGV == -1) {
  printf("run_ic3.pl exmps\n");
  exit(0);
}


qx(rm -f res.txt);
qx(rm -f *.prt);

$exmp_path = "/home/eugene/e0xamples/hwmcc12/multi";

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
 

  $i = 0;
  foreach (@words)  {
   $i++;
   if ($i == 1) {next;}
   printf("   prop. $_\n");
   $ind = $_ - 1;
   $prot_name = $name . _p . $_;


   $pid = fork();
   die if not defined $pid;
   if ($pid > 0) {
#     printf "%d\n",$pid;
     eval {
       local $SIG{ALRM} = sub {kill 9, -$pid; die "alarm\n"};
       alarm 1000;
       waitpid($pid, 0);
       alarm 0;
     };
   }
   elsif ($pid == 0) {
     setpgrp(0,0);
     exec("iic3 < $name.aig -s $ind > $prot_name.prt");
     exit(0);
  }
   
 }

#  printf("%s\n",$num_prop);

  qx(rm -f $name.aig);
}

close EXMPS;


