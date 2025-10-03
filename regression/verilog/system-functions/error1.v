module main;

  parameter P = 1;

  if(P==1)
    $error("something is wrong");

endmodule
