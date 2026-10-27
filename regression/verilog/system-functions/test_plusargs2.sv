// $test$plusargs as the condition of an if statement
// (sv-tests 21.6--test).
module main;
  bit b;
  initial if($test$plusargs("TEST")) b = 1;
endmodule
